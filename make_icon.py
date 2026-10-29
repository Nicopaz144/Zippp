"""Genera el icono de ZipStream (1024x1024, azul y negro) y el catálogo de assets.
Se ejecuta en el workflow antes de XcodeGen. Requiere Pillow."""
import json, os
from PIL import Image, ImageDraw, ImageFilter

S = 2048          # se dibuja al doble y luego se reduce (bordes suaves)
OUT = 1024
cx = S // 2

def vgrad(size, c1, c2):
    g = Image.linear_gradient("L").resize(size)
    return Image.composite(Image.new("RGB", size, c2), Image.new("RGB", size, c1), g)

# Fondo: negro con resplandor azul
img = Image.new("RGB", (S, S), (3, 6, 14))
glow = Image.radial_gradient("L").resize((S, S))
glow = glow.point(lambda v: max(0, int((255 - v) * 0.50)))
img = Image.composite(Image.new("RGB", (S, S), (10, 90, 255)), img, glow)

# Máscara de la figura: cremallera que baja y termina en flecha
m = Image.new("L", (S, S), 0)
d = ImageDraw.Draw(m)

# cursor (slider) con agujero
d.rounded_rectangle([cx - 150, 290, cx + 150, 560], radius=90, fill=255)
d.ellipse([cx - 55, 355, cx + 55, 465], fill=0)

# dientes alternados
tw, th, pitch, gap = 190, 62, 80, 12
y = 600
left = True
while y + th < 1140:
    x0 = cx - gap - tw if left else cx + gap
    d.rounded_rectangle([x0, y, x0 + tw, y + th], radius=34, fill=255)
    left = not left
    y += pitch

# punta de flecha con esquinas redondeadas
r = 46
pts = [(cx - 430 + r, 1190 + r // 2), (cx + 430 - r, 1190 + r // 2), (cx, 1740 - r)]
d.polygon(pts, fill=255)
d.line(pts + [pts[0]], fill=255, width=2 * r, joint="curve")
for px, py in pts:
    d.ellipse([px - r, py - r, px + r, py + r], fill=255)

# resplandor suave detrás de la figura
halo = m.filter(ImageFilter.GaussianBlur(60)).point(lambda v: int(v * 0.55))
img = Image.composite(Image.new("RGB", (S, S), (20, 110, 255)), img, halo)

# relleno degradado azul claro -> azul profundo
fill = vgrad((S, S), (140, 215, 255), (10, 85, 255))
img = Image.composite(fill, img, m)

img = img.resize((OUT, OUT), Image.LANCZOS).convert("RGB")   # sin canal alfa

base = "Sources/Assets.xcassets"
icon_dir = os.path.join(base, "AppIcon.appiconset")
os.makedirs(icon_dir, exist_ok=True)
img.save(os.path.join(icon_dir, "icon.png"))
with open(os.path.join(base, "Contents.json"), "w") as f:
    json.dump({"info": {"author": "xcode", "version": 1}}, f)
with open(os.path.join(icon_dir, "Contents.json"), "w") as f:
    json.dump({"images": [{"filename": "icon.png", "idiom": "universal",
                           "platform": "ios", "size": "1024x1024"}],
               "info": {"author": "xcode", "version": 1}}, f)
print("Icono generado")
